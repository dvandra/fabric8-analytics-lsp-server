/* --------------------------------------------------------------------------------------------
 * Copyright (c) Pavel Odvody 2016
 * Licensed under the Apache-2.0 License. See License.txt in the project root for license information.
 * ------------------------------------------------------------------------------------------ */
'use strict';
import * as path from 'path';
import * as fs from 'fs';
import {
	IPCMessageReader, IPCMessageWriter, createConnection, IConnection,
	TextDocuments, Diagnostic, InitializeResult, CodeLens, CodeAction, RequestHandler, CodeActionParams
} from 'vscode-languageserver';
import { Stream } from 'stream';
import { DependencyCollector, IDependency, IDependencyCollector, PomXmlDependencyCollector, ReqDependencyCollector } from './collector';
import { EmptyResultEngine, SecurityEngine, DiagnosticsPipeline, codeActionsMap, Vul_private, Vul_public, Set_default } from './consumers';

const url = require('url');
const https = require('https');
const request = require('request');
const winston = require('winston');

let transport;
try {
  transport = new winston.transports.File({ filename: '/workspace-logs/ls-bayesian/bayesian.log' });
} catch(err) {
  transport = new winston.transports.Console({ silent: true });
}
const logger = winston.createLogger({
  level: 'debug',
  format: winston.format.simple(),
  transports: [ transport ]
});
logger.info('Starting Bayesian');

enum EventStream {
  Invalid,
  Diagnostics,
  CodeLens
};

let connection: IConnection = null;
/* use stdio for transfer if applicable */
if (process.argv.indexOf('--stdio') == -1)
    connection = createConnection(new IPCMessageReader(process), new IPCMessageWriter(process));
else
    connection = createConnection()

let documents: TextDocuments = new TextDocuments();
documents.listen(connection);

let workspaceRoot: string;
connection.onInitialize((params): InitializeResult => {
    workspaceRoot = params.rootPath;
    return {
        capabilities: {
            textDocumentSync: documents.syncKind,
            codeActionProvider: true
        }
    }
});

interface IFileHandlerCallback {
    (uri: string, name: string, contents: string): void;
};

interface IAnalysisFileHandler {
    matcher:  RegExp;
    stream: EventStream;
    callback: IFileHandlerCallback;
};

interface IAnalysisFiles {
    handlers: Array<IAnalysisFileHandler>;
    file_data: Map<string, string>;
    on(stream: EventStream, matcher: string, cb: IFileHandlerCallback): IAnalysisFiles;
    run(stream: EventStream, uri: string, file: string, contents: string): any;
};

class AnalysisFileHandler implements IAnalysisFileHandler {
    matcher: RegExp;
    constructor(matcher: string, public stream: EventStream, public callback: IFileHandlerCallback) {
        this.matcher = new RegExp(matcher);
    }
};

class AnalysisFiles implements IAnalysisFiles {
    handlers: Array<IAnalysisFileHandler>;
    file_data: Map<string, string>;
    constructor() {
        this.handlers = [];
        this.file_data = new Map<string, string>();
    }
    on(stream: EventStream, matcher: string, cb: IFileHandlerCallback): IAnalysisFiles {
        this.handlers.push(new AnalysisFileHandler(matcher, stream, cb));
        return this;
    }
    run(stream: EventStream, uri: string, file: string, contents: string): any {
        for (let handler of this.handlers) {
            if (handler.stream == stream && handler.matcher.test(file)) {
                return handler.callback(uri, file, contents);
            }
        }
    }
};

interface IAnalysisLSPServer
{
    connection: IConnection;
    files:      IAnalysisFiles;

    handle_file_event(uri: string, contents: string): void;
    handle_code_lens_event(uri: string): CodeLens[];
};

class AnalysisLSPServer implements IAnalysisLSPServer {
    constructor(public connection: IConnection, public files: IAnalysisFiles) {}

    handle_file_event(uri: string, contents: string): void {
        let path_name = url.parse(uri).pathname;
        let file_name = path.basename(path_name);

        this.files.file_data[uri] = contents;

        this.files.run(EventStream.Diagnostics, uri, file_name, contents);
    }

    handle_code_lens_event(uri: string): CodeLens[] {
        let path_name = url.parse(uri).pathname;
        let file_name = path.basename(path_name);
        let lenses = [];
        let contents = this.files.file_data[uri];
        return this.files.run(EventStream.CodeLens, uri, file_name, contents);
    }
};

interface IAggregator
{
    callback: any;
    is_ready(): boolean;
    aggregate(IDependency): void;
};

class Aggregator implements IAggregator
{
    mapping: Map<IDependency, boolean>;
    diagnostics: Array<Diagnostic>;
    constructor(items: Array<IDependency>, public callback: any){
        this.mapping = new Map<IDependency, boolean>();
        for (let item of items) {
            this.mapping.set(item, false);
        }
    }
    is_ready(): boolean {
        let val = true;
        for (let m of this.mapping.entries()) {
            val = val && m[1];
        }
        return val;
    }
    aggregate(dep: IDependency): void {
        this.mapping.set(dep, true);
        if (this.is_ready()) {
            this.callback();
        }
    }
};

class AnalysisConfig
{
    server_url:         string;
    api_token:          string;
    three_scale_user_token:          string;
    forbidden_licenses: Array<string>;
    no_crypto:          boolean;
    home_dir:           string;

    constructor() {
        // TODO: this needs to be configurable
        this.server_url = process.env.RECOMMENDER_API_URL || "api-url-not-available-in-lsp";
        this.api_token = process.env.RECOMMENDER_API_TOKEN || "token-not-available-in-lsp";
        this.three_scale_user_token = process.env.THREE_SCALE_USER_TOKEN || "";
        this.forbidden_licenses = [];
        this.no_crypto = false;
        this.home_dir = process.env[(process.platform == 'win32') ? 'USERPROFILE' : 'HOME'];
    }
};

let config: AnalysisConfig = new AnalysisConfig();
let files: IAnalysisFiles = new AnalysisFiles();
let server: IAnalysisLSPServer = new AnalysisLSPServer(connection, files);
let rc_file = path.join(config.home_dir, '.analysis_rc');
if (fs.existsSync(rc_file)) {
    let rc = JSON.parse(fs.readFileSync(rc_file, 'utf8'));
    if ('server' in rc) {
        config.server_url = `${rc.server}/api/v1`;
    }
}

let DiagnosticsEngines = [SecurityEngine];

const getCAmsg = (deps, diagnostics): string => {
    let msg : string;
    if(diagnostics.length > 0) {
        if (Vul_private > 0 && Vul_public > 0) {
            msg = `Scanned ${deps.length} runtime dependencies, flagged ${Vul_public} Known Security Vulnerability and ${Vul_private} Security Advisory along with quick fixes`;
        } else if (Vul_private == 0 && Vul_public > 0) {
            msg = `Scanned ${deps.length} runtime dependencies, flagged ${Vul_public} Known Security Vulnerability along with quick fixes`;
        } else if (Vul_private > 0 && Vul_public == 0) {
            msg = `Scanned ${deps.length} runtime dependencies, flagged ${Vul_private} Security Advisory`;
        } else {
            msg = `Scanned ${deps.length} runtime dependencies. No potential security vulnerabilities found`;
        }
    } else {
        msg = `Scanned ${deps.length} runtime dependencies. No potential security vulnerabilities found`;
    }
    Set_default(0, 0);
    return msg
};

const caDefaultMsg = 'Checking for security vulnerabilities ...';

const metadataCache = new Map();
const get_metadata = (ecosystem, name, version) => {
    return new Promise((resolve, reject) => {
        const cacheKey = ecosystem + " " + name + " " + version;
        const metadata = metadataCache[cacheKey];
        if (metadata != null) {
            logger.info('cache hit for ' + cacheKey);
            connection.console.log('cache hit for ' + cacheKey);
            resolve(metadata);
        } else {
            const part = [ecosystem, name, version].map(v => encodeURIComponent(v)).join('/');
            const options = {};
                options['url'] = config.server_url;
                if(config.three_scale_user_token){
                    options['url'] += `/component-analyses/${part}?user_key=${config.three_scale_user_token}`;
                } else{
                    options['url'] += `/component-analyses/${part}/`;
                }
                options['headers'] = {
                    'Authorization' : 'Bearer ' + config.api_token,
                };
            logger.debug('get ' + options['url']);
            connection.console.log('Scanning ' + part);
            if(process.env.RECOMMENDER_API_URL){
                request.get(options, (err, httpResponse, body) => {
                    if(err){
                        reject(err);
                    } else {
                        if ((httpResponse.statusCode === 200 || httpResponse.statusCode === 202)) {
                            let response = JSON.parse(body);
                            logger.debug('response ' + response);
                            metadataCache[cacheKey] = response;
                            resolve(response);
                        } else {
                            reject(httpResponse.statusCode);
                        }
                    }
                });
            }
        }
    });
};

let Response = {
    "recommendation": {
        "component_analyses": {
          "vulnerability": [
            {
              "vendor_cve_ids": "CVE-2010-3082",
              "cvss": "1.2",
              "is_private": false
            },
            {
              "vendor_cve_ids": "CVE-2018-1002",
              "cvss": "1.3",
              "is_private": false
            }
          ]
        },
        "recommended_version": "2.3.4",
        "message": "2 vulnerabilities within this dependency",
        "severity": "high",
        "public_vulnerabilities_count": 2,
        "private_vulnerabilities_count": 1,
        "registeration_link": "https://app.snyk.io/login"
    }
};

let Pub_response = {
    "recommendation": {
        "component_analyses": {
          "vulnerability": [
            {
              "vendor_cve_ids": "CVE-2010-3082",
              "cvss": "1.2",
              "is_private": false
            },
            {
              "vendor_cve_ids": "CVE-2018-1002",
              "cvss": "1.3",
              "is_private": false
            }
          ]
        },
        "recommended_version": "2.3.4",
        "message": "2 vulnerabilities within this dependency",
        "severity": "medium",
        "public_vulnerabilities_count": 2,
        "private_vulnerabilities_count": 0,
        "registeration_link": "https://app.snyk.io/login"
    }
};

let Pvt_response = {
    "recommendation": {
        "component_analyses": {
          "vulnerability": [
            {
              "vendor_cve_ids": "CVE-2010-3082",
              "cvss": "1.2",
              "is_private": false
            },
            {
              "vendor_cve_ids": "CVE-2018-1002",
              "cvss": "1.3",
              "is_private": false
            }
          ]
        },
        "recommended_version": null,
        "message": "2 vulnerabilities within this dependency",
        "severity": "high",
        "public_vulnerabilities_count": 0,
        "private_vulnerabilities_count": 2,
        "registeration_link": "https://app.snyk.io/login"
    }
};

let noResponse = {
    "result": {recommendation: {}}
};

let Responses = Array;
Responses[0] = Pub_response;
Responses[1] = noResponse;
Responses[2] = noResponse;
Responses[3] = Pvt_response;
Responses[4] = noResponse;
Responses[5] = noResponse;
Responses[6] = noResponse;
Responses[7] = Response;
Responses[8] = noResponse;
Responses[9] = noResponse;
Responses[10] = noResponse;
Responses[11] = noResponse;
Responses[12] = noResponse;
Responses[13] = noResponse;
Responses[14] = noResponse;
Responses[15] = Pub_response;
Responses[16] = Response;
Responses[17] = noResponse;
Responses[18] = Pub_response;
Responses[19] = Response;
Responses[20] = noResponse;
Responses[21] = Pvt_response;
Responses[22] = noResponse;
Responses[23] = noResponse;
Responses[24] = Response;
Responses[25] = noResponse;
Responses[26] = noResponse;
Responses[27] = Response;

let Default_response = Pub_response;
let i = 0;

const regexVersion =  new RegExp(/^([a-zA-Z0-9]+\.)?([a-zA-Z0-9]+\.)?([a-zA-Z0-9]+\.)?([a-zA-Z0-9]+)$/);
const sendDiagnostics = (ecosystem: string, uri: string, contents: string, collector: IDependencyCollector) => {
    connection.sendNotification('caNotification', {'data': caDefaultMsg});
    collector.collect(contents).then((deps) => {
        let diagnostics = [];
        /* Aggregate asynchronous requests and send the diagnostics at once */
        let aggregator = new Aggregator(deps, () => {
            connection.sendNotification('caNotification', {'data': getCAmsg(deps, diagnostics), 'diagCount' : diagnostics.length > 0? diagnostics.length : 0});
            connection.sendDiagnostics({uri: uri, diagnostics: diagnostics});
        });
        
        for (let dependency of deps) {
            if(dependency.name.value && dependency.version.value && regexVersion.test(dependency.version.value.trim())) {
                get_metadata(ecosystem, dependency.name.value, dependency.version.value).then((response) => {
                    if (response != null && response[0] != {}) {
                        let pipeline = new DiagnosticsPipeline(DiagnosticsEngines, dependency, config, diagnostics, uri);
                        
                        if (i == 0) {
                            pipeline.run(Pub_response);
                            i = 1;
                        } else if (i == 1) {
                            pipeline.run(Pvt_response);
                            i = 2;
                        } else {
                            pipeline.run(Response);
                        }
                    }
                    aggregator.aggregate(dependency);
                }).catch((err)=>{
                    aggregator.aggregate(dependency);
                    connection.console.log(`Error ${err} while ${dependency.name.value}:${dependency.version.value}`);
                });
            } else {
                aggregator.aggregate(dependency);
            }
        }
    });
};

files.on(EventStream.Diagnostics, "^package\\.json$", (uri, name, contents) => {
    sendDiagnostics('npm', uri, contents, new DependencyCollector(null));
});

files.on(EventStream.Diagnostics, "^pom\\.xml$", (uri, name, contents) => {
    sendDiagnostics('maven', uri, contents, new PomXmlDependencyCollector());
});


files.on(EventStream.Diagnostics, "^requirements\\.txt$", (uri, name, contents) => {
    sendDiagnostics('pypi', uri, contents, new ReqDependencyCollector());
});

let checkDelay;
connection.onDidSaveTextDocument((params) => {
    clearTimeout(checkDelay);
    server.handle_file_event(params.textDocument.uri, server.files.file_data[params.textDocument.uri]);
});

connection.onDidChangeTextDocument((params) => {
    /* Update internal state for code lenses */
    server.files.file_data[params.textDocument.uri] = params.contentChanges[0].text;
    clearTimeout(checkDelay);
    checkDelay = setTimeout(() => {
        server.handle_file_event(params.textDocument.uri, server.files.file_data[params.textDocument.uri])
    }, 500)
});

connection.onDidOpenTextDocument((params) => {
    server.handle_file_event(params.textDocument.uri, params.textDocument.text);
});

connection.onCodeAction((params, token): CodeAction[] => {
    clearTimeout(checkDelay);
    let codeActions: CodeAction[] = [];
    for (let diagnostic of params.context.diagnostics) {
        let codeAction = codeActionsMap[diagnostic.message];
        if (codeAction != null) {
            codeActions.push(codeAction)
        }
    }
    return codeActions;
});

connection.onDidCloseTextDocument((params) => {
    clearTimeout(checkDelay);
});

connection.listen();
